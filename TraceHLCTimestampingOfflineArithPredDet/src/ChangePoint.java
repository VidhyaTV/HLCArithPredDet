class ChangePoint
{
    Clock cPointTimestamp;
    int endpointType;//+1 for left endpoint, -1 for right endpoint
    ChangePoint(Clock cPtTimestamp, int ePoint)
    {
        cPointTimestamp=cPtTimestamp;
        endpointType=ePoint;
    }
    Clock getcPointTimestamp()
    {
        return cPointTimestamp;
    }
    int getEndPointType()
    {
        return endpointType;
    }
    void setcPointTimestamp(Clock cPtTimestamp)
    {
        cPointTimestamp=cPtTimestamp;
    }
    void setEndPointType(int ePoint)
    {
        endpointType=ePoint;
    }
}